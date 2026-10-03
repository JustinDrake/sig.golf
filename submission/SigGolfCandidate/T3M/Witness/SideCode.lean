import SigGolfCandidate.T3M.Witness.Layout

namespace SigGolfCandidate.T3M.SideCode
set_option autoImplicit false

def sideWidth (a : Nat) : Nat := min a 3
def sideHeader (a merge node : Nat) : Nat := a + 16*merge + 32*(node % 8)

theorem sideHeader_fields (a merge node : Nat) (ha : a < 16) (hm : merge < 2) :
    sideHeader a merge node < 256 ∧ sideHeader a merge node % 16 = a ∧
    sideHeader a merge node / 16 % 2 = merge ∧ sideHeader a merge node / 32 = node % 8 := by
  have hn := Nat.mod_lt node (by decide : 0 < 8)
  unfold sideHeader
  omega

theorem segSideMod_dvd_eight (a : Nat) : segSideMod a ∣ 8 := by
  have h : sideWidth a ≤ 3 := Nat.min_le_right _ _
  have hd := Nat.pow_dvd_pow 2 h
  exact hd

theorem heap_low_bits (g lo a : Nat) (h : lo+a ≤ 11) :
    (2048+g)/2^lo % segSideMod a = g/2^lo % segSideMod a := by
  have hlo : lo ≤ 11 := by omega
  have hp : 2048 = 2^(11-lo)*2^lo := by
    rw [← pow_add,Nat.sub_add_cancel hlo]
    norm_num
  rw [hp,Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.two_pow_pos lo)]
  have hwidth : sideWidth a ≤ 11-lo := by
    have := Nat.min_le_left a 3
    unfold sideWidth
    omega
  have hd : segSideMod a ∣ 2^(11-lo) := Nat.pow_dvd_pow 2 hwidth
  rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,Nat.add_zero,Nat.mod_mod]

theorem honest_sideHeader_check (g lo a merge : Nat) (h : lo+a ≤ 11) (hm : merge < 2) :
    sideHeader a merge (g/2^lo) / 32 % segSideMod a = (2048+g)/2^lo % segSideMod a := by
  have hf := sideHeader_fields a merge (g/2^lo) (by omega) hm
  rw [hf.2.2.2,Nat.mod_mod_of_dvd _ (segSideMod_dvd_eight a),heap_low_bits g lo a h]

theorem check_preserves_original_parity (b E a : Nat) (ha : 0 < a)
    (h : b/32 % segSideMod a = E % segSideMod a) : b/32 % 2 = E % 2 := by
  have hd : 2 ∣ segSideMod a := by
    have hw : 1 ≤ sideWidth a := by unfold sideWidth;omega
    have hh := Nat.pow_dvd_pow 2 hw
    simpa only [segSideMod,sideWidth,pow_one] using hh
  have he := congrArg (fun n => n%2) h
  simpa only [Nat.mod_mod_of_dvd _ hd] using he

end SigGolfCandidate.T3M.SideCode
