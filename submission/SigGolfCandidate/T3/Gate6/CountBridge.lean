import SigGolfCandidate.T3.Gate6.ChildCounting
namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
attribute [local irreducible] Finset.univ Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 5000

theorem family_card_packed_generic (y cap : Nat) (hy : 3≤y) (hc : 341376^7<y-1) :
    (univ.filter (fun s : SetFamily => familyCost s≤cap)).card =
      ((((Q y 7).coeff 3)^7)%y^(cap+1))%(y-1) := by
  classical
  have h := generic_capped_card familyCost y cap hy (by rw [family_card];exact hc)
  rw [family_weight_sum] at h
  convert h using 1

theorem coefficient_power_mod (K y M H j n : Nat) (hm : 1<M) (hj : j≤K) :
    ((Q y H).coeff j)^n%M = ((piter K y M H [0,1]).getD j 0)^n%M := by
  have hp := rep_piter (K:=K) (y:=y) (M:=M) H 0 [0,1] (rep_zero K y M hm) j hj
  rw [Nat.zero_add] at hp
  rw [hp,←Nat.pow_mod]

end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.family_card_packed_generic
#print axioms SigGolfResearch.Gate6.coefficient_power_mod
