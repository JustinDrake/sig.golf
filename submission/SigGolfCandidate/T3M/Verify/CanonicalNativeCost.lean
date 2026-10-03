import SigGolfCandidate.T3M.Verify.CanonicalBank
import SigGolfCandidate.T3M.Verify.CanonicalDispatchTyped

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative

/-- Fourteen dispatch/return instructions plus the verified five-segment cost
equals the original schedule potential less four. The potential's caller
allowance is therefore not mistaken for the actual segment instruction count. -/
theorem bank_cost_exact : ∀ (x y : Fin 8), 0<x.val → 0<y.val → x≠y →
    14+bankCost (geomIndex x.val y.val) 0 5+4=
      CanonicalCost.bankCost (SideCost.bankShape x.val y.val) := by decide +kernel

theorem bank_cost_cap (x y : Nat) (hx : 0<x ∧ x<8) (hy : 0<y ∧ y<8) (hne : x≠y) :
    14+bankCost (geomIndex x y) 0 5+4 ≤
      CanonicalCost.cap ((SideCost.bankShape x y).sum) := by
  have hfin : (⟨x,hx.2⟩ : Fin 8)≠⟨y,hy.2⟩ := by
    intro h; exact hne (congrArg Fin.val h)
  rw [bank_cost_exact ⟨x,hx.2⟩ ⟨y,hy.2⟩ hx.1 hy.1 hfin]
  exact (CanonicalCost.bank_cap ⟨x,hx.2⟩ ⟨y,hy.2⟩ hx.1 hy.1 hfin).2.2

def geometryCosts (pairs : List (Nat × Nat)) : List Nat :=
  pairs.map fun p => 14+bankCost (geomIndex p.1 p.2) 0 5

theorem geometry_cost_sum (pairs : List (Nat × Nat))
    (hok : ∀ p∈pairs, (0<p.1 ∧ p.1<8) ∧ (0<p.2 ∧ p.2<8) ∧ p.1≠p.2) :
    (geometryCosts pairs).sum+4*pairs.length=
      ((pairs.map fun p => SideCost.bankShape p.1 p.2).map CanonicalCost.bankCost).sum := by
  induction pairs with
  | nil => simp [geometryCosts]
  | cons p rest ih =>
    have hp := hok p (by simp)
    have hr := ih (fun q hq => hok q (by simp [hq]))
    have he := bank_cost_exact ⟨p.1,hp.1.2⟩ ⟨p.2,hp.2.1.2⟩ hp.1.1 hp.2.1.1
      (by intro h; exact hp.2.2 (congrArg Fin.val h))
    dsimp only at he
    simp only [geometryCosts,List.map_cons,List.sum_cons,List.length_cons] at hr ⊢
    omega

/-- FTS-only integration cost, conditional on the seven geometries and the
accepted 115-fold cap. The 89 fixed cycles are 31 entry/setup, 30 caller
advances, 5 restoration, and 23 forest finishing cycles. -/
theorem seven_integration_bound (pairs : List (Nat × Nat)) (hlen : pairs.length=7)
    (hok : ∀ p∈pairs, (0<p.1 ∧ p.1<8) ∧ (0<p.2 ∧ p.2<8) ∧ p.1≠p.2)
    (hfold : ((pairs.map fun p => SideCost.bankShape p.1 p.2).map List.sum).sum ≤ 115) :
    89+(geometryCosts pairs).sum ≤ 2322 := by
  have he := geometry_cost_sum pairs hok
  have hb := CanonicalCost.projected_seven_exact
    (pairs.map fun p => SideCost.bankShape p.1 p.2) (by simpa using hlen) hfold (by
      intro xs hxs
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hxs
      have hp' := hok p hp
      have hc := CanonicalCost.bank_cap ⟨p.1,hp'.1.2⟩ ⟨p.2,hp'.2.1.2⟩ hp'.1.1 hp'.2.1.1
        (by intro h; exact hp'.2.2 (congrArg Fin.val h))
      dsimp only at hc
      exact ⟨hc.1,by have := hc.2.1; omega,hc.2.2⟩)
  rw [hlen] at he
  omega

#print axioms seven_integration_bound
end SigGolfCandidate.T3M.CanonicalNative
