import SigGolfCandidate.T3M.Verify.CanonicalBlocks
import SigGolfCandidate.T3M.Witness.CanonicalCost

/-! The instruction metadata has exactly the five-segment canonical shape. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.T3M

def geomIndex (x y : Nat) : Nat := (x-1)*6+(y-1)-(if x<y then 1 else 0)
def outline (p : BlockPlan) : Option Nat × Nat × Nat × Nat :=
  (p.leaf,p.folds,p.variant,p.depth)
def expectedOutline (x y : Nat) : List (Option Nat × Nat × Nat × Nat) :=
  if x<y then
    [(some 0,x-1,1,0),(some 1,x-1,0,1),(none,y-1-x,1,0),
      (some 2,y-1,0,1),(none,11-y,2,0)]
  else
    [(some 0,x-1,1,0),(some 1,y-1,1,1),(some 2,y-1,0,2),
      (none,x-1-y,0,1),(none,11-x,2,0)]

theorem plan_shape : ∀ (x y : Fin 8), 0<x.val → 0<y.val → x≠y →
    geomIndex x.val y.val<42 ∧
      (((plans[geomIndex x.val y.val]!).toList).map outline)=expectedOutline x.val y.val :=
  by decide +kernel

theorem plan_bounds : ∀ (g : Fin 42) (j : Fin 5),
    let p := plan g.val j.val
    p.folds ≤ 10 ∧ p.depth ≤ 2 ∧ p.variant ≤ 2 ∧
      (∀ k∈p.leaf, k<3) ∧ p.hashes.size=2 ∧ p.rungs.size=2 ∧
      (∀ side : Fin 2, (p.hashes[side.val]!).size=p.folds+1 ∧
        (p.rungs[side.val]!).size=p.folds) := by decide +kernel

theorem plan_folds : ∀ (x y : Fin 8), 0<x.val → 0<y.val → x≠y →
    ((List.range 5).map fun j => (plan (geomIndex x.val y.val) j).folds)=
      SideCost.bankShape x.val y.val := by decide +kernel

theorem geometry_fold_budget (x y : Nat) (hx : 0<x ∧ x<8) (hy : 0<y ∧ y<8) (hne : x≠y) :
    10 ≤ ((List.range 5).map fun j => (plan (geomIndex x y) j).folds).sum ∧
      ((List.range 5).map fun j => (plan (geomIndex x y) j).folds).sum ≤ 20 := by
  have hfin : (⟨x,hx.2⟩ : Fin 8)≠⟨y,hy.2⟩ := by
    intro he; exact hne (congrArg Fin.val he)
  rw [plan_folds ⟨x,hx.2⟩ ⟨y,hy.2⟩ hx.1 hy.1 hfin]
  have h := CanonicalCost.bank_cap ⟨x,hx.2⟩ ⟨y,hy.2⟩ hx.1 hy.1 hfin
  exact ⟨h.1,h.2.1⟩

end SigGolfCandidate.T3M.CanonicalNative
